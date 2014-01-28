/*********************                                                        */
/*! \file theory_rewriterules_rules.cpp
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

#include "theory/rewriterules/theory_rewriterules_rules.h"
#include "theory/rewriterules/theory_rewriterules_params.h"
#include "theory/rewriterules/theory_rewriterules_preprocess.h"
#include "theory/rewriterules/theory_rewriterules.h"
#include "theory/rewriterules/options.h"

#include "theory/quantifiers/term_database.h"

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

// TODO replace by a real dictionnary
// We should create a real substitution? slower more precise
// We don't do that often
bool nonunifiable( TNode t0, TNode pattern, const std::vector<Node> & vars){
  typedef std::vector<std::pair<TNode,TNode> > tstack;
  tstack stack(1,std::make_pair(t0,pattern)); // t * pat

  while(!stack.empty()){
    const std::pair<TNode,TNode> p = stack.back(); stack.pop_back();
    const TNode & t = p.first;
    const TNode & pat = p.second;

    // t or pat is a variable currently we consider that can match anything
    if( find(vars.begin(),vars.end(),t) != vars.end() ) continue;
    if( pat.getKind() == INST_CONSTANT ) continue;

    // t and pat are nonunifiable
    if( !Trigger::isAtomicTrigger( t ) || !Trigger::isAtomicTrigger( pat ) ) {
      if(t == pat) continue;
      else return true;
    };
    if( t.getOperator() != pat.getOperator() ) return true;

    //put the children on the stack
    for( size_t i=0; i < pat.getNumChildren(); i++ ){
      stack.push_back(std::make_pair(t[i],pat[i]));
    };
  }
  // The heuristic can't find non-unifiability
  return false;
}


void TheoryRewriteRules::computeMatchBody ( const RewriteRule * rule,
                                            size_t start){
  std::vector<TNode> stack(1,rule->new_terms);

  while(!stack.empty()){
    Node t = stack.back(); stack.pop_back();

    // We don't want to consider variable in t
    if( std::find(rule->free_vars.begin(), rule->free_vars.end(), t)
        != rule->free_vars.end()) continue;
    // t we want to consider only UF function
    if( t.getKind() == APPLY_UF ){
      for(size_t rid = start, end = d_rules.size(); rid < end; ++rid) {
        RewriteRule * r = d_rules[rid];
        if(r->d_split || r->trigger_for_body_match == NULL) continue;
        //the split rules are not computed and the one with multi-pattern
        if( !nonunifiable(t, r->trigger_for_body_match->d_pattern, rule->free_vars)){
          rule->body_match.push_back(std::make_pair(t,r));
        }
      }
    }

    //put the children on the stack
    for( size_t i=0; i < t.getNumChildren(); i++ ){
      stack.push_back(t[i]);
    };

  }
}

inline void addPattern(TheoryRewriteRules & re,
                       TNode tri,
                       std::vector<Node> & pattern,
                       std::vector<Node> & vars,
                       std::vector<Node> & inst_constants,
                       TNode r){
  if (tri.getKind() == kind::NOT && tri[0].getKind() == kind::APPLY_UF)
    tri = tri[0];
  pattern.push_back(
                    options::rewriteRulesAsAxioms()?
                    static_cast<Node>(tri):
                    re.getQuantifiersEngine()->getTermDatabase()->
                    convertNodeToPattern(tri,r,vars,inst_constants));
}

/*** Check that triggers contains all the variables */
void checkPatternVarsAux(TNode pat,const std::vector<Node> & vars,
                         std::vector<bool> & seen){
  for(size_t id=0;id < vars.size(); ++id){
    if(pat == vars[id]){
      seen[id]=true;
      break;
    };
  };
  for(Node::iterator i = pat.begin(); i != pat.end(); ++i) {
    checkPatternVarsAux(*i,vars,seen);
  };
}

bool checkPatternVars(const std::vector<Node> & pattern,
                      const std::vector<Node> & vars){
  std::vector<bool> seen(vars.size(),false);
  for(std::vector<Node>::const_iterator i = pattern.begin();
      i != pattern.end(); ++i) {
    checkPatternVarsAux(*i,vars,seen);
  };
  return (find(seen.begin(),seen.end(),false) == seen.end());
}

/** Main function for construction of RewriteRule */
void TheoryRewriteRules::addRewriteRule(const Node r)
{
  Assert(r.getKind() == kind::REWRITE_RULE);
  Kind rrkind = r[2].getKind();
  /*   Replace variables by Inst_* variable and tag the terms that
       contain them */
  std::vector<Node> vars;
  vars.reserve(r[0].getNumChildren());
  for( Node::const_iterator v = r[0].begin(); v != r[0].end(); ++v ){
    vars.push_back(*v);
  };
  /* Instantiation version */
  std::vector<Node> inst_constants = createInstVariable(r,vars);
  /* Body/Remove_term/Guards/Triggers */
  Node body = r[2][1];
  TNode new_terms = r[2][1];
  std::vector<Node> guards;
  std::vector<Node> pattern;
  std::vector<Node> to_remove;  /* "remove" the terms from the database
                                   when fired */
  /* shortcut */
  TNode head = r[2][0];
  TypeNode booleanType = NodeManager::currentNM()->booleanType();
  switch(rrkind){
  case kind::RR_REWRITE:
    /* Equality */
    to_remove.push_back(head);
    addPattern(*this,head,pattern,vars,inst_constants,r);
    if(head.getType(false) == booleanType) body = head.iffNode(body);
    else body = head.eqNode(body);
    break;
  case kind::RR_REDUCTION:
    /** Add head to remove */
      for(Node::iterator i = head.begin(); i != head.end(); ++i) {
        to_remove.push_back(*i);
      };
  case kind::RR_DEDUCTION:
    /** Add head to guards and pattern */
    switch(head.getKind()){
    case kind::AND:
      guards.reserve(head.getNumChildren());
      for(Node::iterator i = head.begin(); i != head.end(); ++i) {
        guards.push_back(*i);
        addPattern(*this,*i,pattern,vars,inst_constants,r);
      };
      break;
    default:
      if (head != d_true){
        guards.push_back(head);
        addPattern(*this,head,pattern,vars,inst_constants,r);
      };
      /** otherwise guards is empty */
    };
    break;
  default:
    Unreachable("RewriteRules can be of only three kinds");
  };
  /* Add the other guards */
  TNode g = r[1];
  switch(g.getKind()){
  case kind::AND:
    guards.reserve(g.getNumChildren());
    for(Node::iterator i = g.begin(); i != g.end(); ++i) {
      guards.push_back(*i);
    };
    break;
  default:
    if (g != d_true) guards.push_back(g);
    /** otherwise guards is empty */
  };
  /* Add the other triggers */
  if( r[2].getNumChildren() >= 3 )
    for(Node::iterator i = r[2][2][0].begin(); i != r[2][2][0].end(); ++i) {
      // todo test during typing that its a good term (no not, atom, or term...)
      addPattern(*this,*i,pattern,vars,inst_constants,r);
    };
  // Assert(pattern.size() == 1, "currently only single pattern are supported");




  //If we convert to usual axioms
  if(options::rewriteRulesAsAxioms()){
    NodeBuilder<> forallB(kind::FORALL);
    forallB << r[0];
    NodeBuilder<> guardsB(kind::AND);
    guardsB.append(guards);
    forallB << normalizeConjunction(guardsB).impNode(body);
    NodeBuilder<> patternB(kind::INST_PATTERN);
    patternB.append(pattern);
    NodeBuilder<> patternListB(kind::INST_PATTERN_LIST);
    patternListB << static_cast<Node>(patternB);
    forallB << static_cast<Node>(patternListB);
    Node lem = (Node) forallB;
    lem = Rewriter::rewrite(lem);
    QRewriteRuleAttribute qra;
    lem.setAttribute(qra,r);
    getOutputChannel().lemma(lem);
    return;
  }

  //turn all to propagate
  // if(true){
  //   NodeBuilder<> guardsB(kind::AND);
  //   guardsB.append(guards);
  //   body = normalizeConjunction(guardsB).impNode(body);
  //   guards.clear();
  //   rrkind = kind::RR_DEDUCTION;
  // }


  //Every variable must be seen in the pattern
  if (!checkPatternVars(pattern,inst_constants)){
    Warning() << Node::setdepth(-1) << "The rule" << r <<
      " has been removed since it doesn't contain every variables."
              << std::endl;
    return;
  }


  //Add to direct rewrite rule
  bool directrr = false;
  if(direct_rewrite &&
     guards.size() == 0 && rrkind == kind::RR_REWRITE
     && pattern.size() == 1){
    directrr = addRewritePattern(pattern[0],new_terms, inst_constants, vars);
  }


  // final construction
  Trigger trigger = createTrigger(r,pattern);
  ApplyMatcher * applymatcher =
    pattern.size() == 1 && pattern[0].getKind() == kind::APPLY_UF?
    new ApplyMatcher(pattern[0],getQuantifiersEngine()) : NULL;
  RewriteRule * rr = new RewriteRule(*this, trigger, applymatcher,
                                     guards, body, new_terms,
                                     vars, inst_constants, to_remove,
                                     directrr);
  /** other -> rr */
  if(compute_opt && !rr->d_split) computeMatchBody(rr);
  d_rules.push_back(rr);
  /** rr -> all (including himself) */
  if(compute_opt && !rr->d_split)
    for(size_t rid = 0, end = d_rules.size(); rid < end; ++rid)
      computeMatchBody(d_rules[rid],
                       d_rules.size() - 1);

  Debug("rewriterules::new") << "created rewriterule"<< (rr->d_split?"(split)":"") << ":(" << d_rules.size() - 1 << ")"
                        << *rr << std::endl;

}


bool willDecide(TNode node, bool positive = true){
  /* TODO something better */
  switch(node.getKind()) {
  case AND:
    return !positive;
  case OR:
    return positive;
  case IFF:
    return true;
  case XOR:
    return true;
  case IMPLIES:
    return true;
  case ITE:
    return true;
  case NOT:
    return willDecide(node[0],!positive);
  default:
    return false;
  }
}

static size_t id_next = 0;
RewriteRule::RewriteRule(TheoryRewriteRules & re,
                         Trigger & tr, ApplyMatcher * applymatcher,
                         std::vector<Node> & g, Node b, TNode nt,
                         std::vector<Node> & fv,std::vector<Node> & iv,
                         std::vector<Node> & to_r, bool drr) :
  id(++id_next), d_split(willDecide(b)),
  trigger(tr), body(b), new_terms(nt), free_vars(), inst_vars(),
  body_match(re.getSatContext()),trigger_for_body_match(applymatcher),
  d_cache(re.getSatContext(),re.getQuantifiersEngine()), directrr(drr){
  free_vars.swap(fv); inst_vars.swap(iv); guards.swap(g); to_remove.swap(to_r);
};


bool RewriteRule::inCache(TheoryRewriteRules & re, rrinst::InstMatch & im)const{
  bool res = !d_cache.addInstMatch(im);
  Debug("rewriterules::matching") << "rewriterules::cache " << im
                                  << (res ? " HIT" : " MISS") << std::endl;
  return res;
};

/** A rewrite rule */
void RewriteRule::toStream(std::ostream& out) const{
  out << "[" << id << "] ";
  for(std::vector<Node>::const_iterator
        iter = guards.begin(); iter != guards.end(); ++iter){
    out << *iter;
  };
  out << "=>" << body << std::endl;
  out << "{";
  for(BodyMatch::const_iterator
        iter = body_match.begin(); iter != body_match.end(); ++iter){
    out << (*iter).first << "[" << (*iter).second->id << "]" << ",";
  };
  out << "}" << (directrr?"*":"") << std::endl;
}

RewriteRule::~RewriteRule(){
  Debug("rewriterule::stats") << *this
                             << "  (" << nb_matched
                             << ","   << nb_applied
                             << ","   << nb_propagated
                             << ")" << std::endl;
  delete(trigger_for_body_match);
}

bool TheoryRewriteRules::addRewritePattern(TNode pattern, TNode body,
                                           rewriter::Subst & pvars,
                                           rewriter::Subst & vars){
  Assert(pattern.getKind() == kind::APPLY_UF);
  TNode op = pattern.getOperator();
  TheoryRewriteRules::RegisterRRPpRewrite::iterator i =
    d_registeredRRPpRewrite.find(op);

  rewriter::RRPpRewrite * p;
  if (i == d_registeredRRPpRewrite.end()){
    p = new rewriter::RRPpRewrite();
    d_registeredRRPpRewrite.insert(std::make_pair(op,p));
    ((uf::TheoryUF*)getQuantifiersEngine()->getTheoryEngine()->theoryOf( THEORY_UF ))->
      registerPpRewrite(op,p);
  } else p = i->second;

  return p->addRewritePattern(pattern,body,pvars,vars);

}

std::vector<Node> TheoryRewriteRules::createInstVariable( Node r, std::vector<Node> & vars ){
  std::vector<Node> inst_constant;
  inst_constant.reserve(vars.size());
  for( std::vector<Node>::const_iterator v = vars.begin();
       v != vars.end(); ++v ){
    //make instantiation constants
    Node ic = NodeManager::currentNM()->mkInstConstant( (*v).getType() );
    inst_constant.push_back( ic );
    InstConstantAttribute ica;
    ic.setAttribute(ica,r);
    //also set the no-match attribute
    NoMatchAttribute nma;
    ic.setAttribute(nma,true);
  };
  return inst_constant;
}


}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

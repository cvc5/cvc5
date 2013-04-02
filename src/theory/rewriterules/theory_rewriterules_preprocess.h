/*********************                                                        */
/*! \file theory_rewriterules_preprocess.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief One utilitise for rewriterules definition
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PREPROCESS_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PREPROCESS_H

#include <vector>
#include <ext/hash_set>
#include <ext/hash_map>
#include "expr/expr.h"
#include "expr/node.h"
#include "theory/rewriterules/theory_rewriterules_params.h"
#include "theory/uf/theory_uf.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {

namespace rewriter {

  typedef Node TMPNode;
  typedef std::vector<Node> Subst;
  typedef std::vector<Expr> ESubst;
  typedef std::vector<TMPNode> TSubst;

  struct Step{

    /** match the node and add in Vars the found variables */
    virtual Node run(TMPNode node) = 0;
    virtual bool add(TMPNode pattern, TMPNode body, Subst & pvars, Subst & vars) = 0;
  };/* struct Step */

  struct FinalStep : Step {
    Node body;
    TSubst vars;

    Node subst(Subst & subst){
      return body.substitute(vars.begin(), vars.end(),
                             subst.begin(), subst.end());
    }

  };/* struct FinalStep */

  typedef std::hash_map< Node, int, NodeHashFunction > PVars;

  struct Pattern : FinalStep{
    Node pattern;
    PVars pattern_vars;

    Node run(TMPNode node){
      Subst vars = Subst(pattern_vars.size(),Node::null());

      typedef std::vector<std::pair<TMPNode,TMPNode> > tstack;
      tstack stack(1,std::make_pair(node,pattern)); // t * pat

      while(!stack.empty()){
        const std::pair<TMPNode,TMPNode> p = stack.back(); stack.pop_back();
        const TMPNode & t = p.first;
        const TMPNode & pat = p.second;

        // pat is a variable
        if( pat.getKind() == kind::INST_CONSTANT ||
            pat.getKind() == kind::VARIABLE){
          PVars::iterator i = pattern_vars.find(pat);
          Assert(i != pattern_vars.end());
          if(vars[i->second].isNull()) vars[i->second] = t;
          if(vars[i->second] == t) continue;
          return Node::null();
        };

        // t is not an UF application
        if( t.getKind() != kind::APPLY_UF ){
          if (t == pat) continue;
          else return Node::null();
        };

        //different UF_application
        if( t.getOperator() != pat.getOperator() ) return Node::null();

        //put the children on the stack
        for( size_t i=0; i < pat.getNumChildren(); i++ ){
          stack.push_back(std::make_pair(t[i],pat[i]));
        };
      }

      // Matching is done
      return subst(vars);
    }

    bool add(TMPNode pattern, TMPNode body, Subst & pvars, Subst & vars){
      return false;
    }
    
  };/* struct Pattern */


  struct Args : Step {
    typedef std::vector<Pattern> Patterns;
    Patterns d_matches;

    Node run(TMPNode node){
      Node n;
      for (Patterns::iterator i = d_matches.begin();
           i != d_matches.end() && n.isNull(); ++i){
        Debug("rewriterules-rewrite") << "test?" << i->pattern << std::endl;
        n = i->run(node);
      }
      return n;
    }

    bool add(TMPNode pattern, TMPNode body, Subst & pvars, Subst & vars){
      Debug("rewriterules-rewrite") << "theoryrewrite::Args::add" << "("
                                    << d_matches.size() << ")"
                                    << pattern << "->" << body << std::endl;
      d_matches.push_back(Pattern());
      Pattern & p = d_matches.back();
      p.body = body;
      p.vars.reserve(vars.size());
      for( size_t i=0; i < vars.size(); i++ ){
        p.vars.push_back(vars[i]);
      };
      p.pattern = pattern;
      for( size_t i=0; i < pvars.size(); i++ ){
        p.pattern_vars[pvars[i]] = i;
      };
      return true;
    };

    void clear(){
      d_matches.clear();
    }
  };/* struct Args */

class RRPpRewrite : public uf::TheoryUF::PpRewrite {
  Args d_pattern;
public:
  Node ppRewrite(TNode node){
    Debug("rewriterules-rewrite") << "rewrite?" << node << std::endl;
    Node t = d_pattern.run(node);
    Debug("rewriterules-rewrite") << "rewrite:" << node
                                  << (t.isNull()? " to": " to ")
                                  << t << std::endl;
    if (t.isNull()) return node;
    else return t;
  }

  bool addRewritePattern(TMPNode pattern, TMPNode body,
                                Subst & pvars, Subst & vars){
    return d_pattern.add(pattern,body,pvars,vars);
  }

};/* class RRPpRewrite */



}/* CVC4::theory::rewriterules::rewriter namespace */

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_PREPROCESS_H */

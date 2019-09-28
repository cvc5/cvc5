/*********************                                                        */
/*! \file ce_guided_single_inv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H
#define CVC4__THEORY__QUANTIFIERS__CE_GUIDED_SINGLE_INV_H

#include "context/cdlist.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/inst_match_trie.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv_sol.h"
#include "theory/quantifiers/sygus/transition_inference.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;

// this class infers whether a conjecture is single invocation (Reynolds et al CAV 2015), and sets up the
// counterexample-guided quantifier instantiation utility (d_cinst), and methods for solution
// reconstruction (d_sol).
// It also has more advanced techniques for:
// (1) partitioning a conjecture into single invocation / non-single invocation portions for invariant synthesis,
// (2) inferring whether the conjecture corresponds to a deterministic transistion system (by utility d_ti).
// For these techniques, we may generate a template (d_templ) which specifies a restricted
// solution space. We may in turn embed this template as a SyGuS grammar.
class CegSingleInv
{
 private:
  friend class CegqiOutputSingleInv;
  //presolve
  void collectPresolveEqTerms( Node n,
                               std::map< Node, std::vector< Node > >& teq );
  void getPresolveEqConjuncts( std::vector< Node >& vars,
                               std::vector< Node >& terms,
                               std::map< Node, std::vector< Node > >& teq,
                               Node n, std::vector< Node >& conj );
  Node postProcessSolution(Node n);
 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** the parent of this class */
  SynthConjecture* d_parent;
  // single invocation inference utility
  SingleInvocationPartition* d_sip;
  // transition inference module for each function to synthesize
  std::map< Node, TransitionInference > d_ti;
  // solution reconstruction
  CegSingleInvSol* d_sol;

  // list of skolems for each argument of programs
  std::vector<Node> d_single_inv_arg_sk;
  // list of variables/skolems for each program
  std::vector<Node> d_single_inv_var;
  std::vector<Node> d_single_inv_sk;
  std::map<Node, int> d_single_inv_sk_index;
  // program to solution index
  std::map<Node, unsigned> d_prog_to_sol_index;
  // original conjecture
  Node d_orig_conjecture;
  // solution
  Node d_orig_solution;
  Node d_solution;
  Node d_sygus_solution;

 public:
  //---------------------------------representation of the solution
  /**
   * The list of instantiations that suffice to show the first-order equivalent
   * of the negated synthesis conjecture is unsatisfiable.
   */
  std::vector<std::vector<Node> > d_inst;
  /**
   * The list of instantiation lemmas, corresponding to instantiations of the
   * first order conjecture for the term vectors above.
   */
  std::vector<Node> d_instConds;
  /** is solved */
  bool d_isSolved;
  //---------------------------------end representation of the solution

 private:
  // conjecture
  Node d_quant;
  Node d_simp_quant;
  // are we single invocation?
  bool d_single_invocation;
  // single invocation portion of quantified formula
  Node d_single_inv;
  // transition relation version per program
  std::map< Node, Node > d_trans_pre;
  std::map< Node, Node > d_trans_post;
  // the template for each function to synthesize
  std::map< Node, Node > d_templ;
  // the template argument for each function to synthesize (occurs in exactly one position of its template)
  std::map< Node, Node > d_templ_arg;
  
 public:
  CegSingleInv(QuantifiersEngine* qe, SynthConjecture* p);
  ~CegSingleInv();

  // get simplified conjecture
  Node getSimplifiedConjecture() { return d_simp_quant; }
 public:
  // initialize this class for synthesis conjecture q
  void initialize( Node q );
  /** finish initialize
   *
   * This method sets up final decisions about whether to use single invocation
   * techniques.
   *
   * The argument syntaxRestricted is whether the syntax for solutions for the
   * initialized conjecture is restricted.
   */
  void finishInit(bool syntaxRestricted);
  /** solve
   *
   * If single invocation techniques are being used, it solves
   * the first order form of the negated synthesis conjecture using a fresh
   * copy of the SMT engine. This method returns true if it has successfully
   * found a solution to the synthesis conjecture using this method.
   */
  bool solve();
  //get solution
  Node getSolution( unsigned sol_index, TypeNode stn, int& reconstructed, bool rconsSygus = true );
  //reconstruct to syntax
  Node reconstructToSyntax( Node s, TypeNode stn, int& reconstructed,
                            bool rconsSygus = true );
  // is single invocation
  bool isSingleInvocation() const { return !d_single_inv.isNull(); }
  /** preregister conjecture */
  void preregisterConjecture( Node q );

  Node getTransPre(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_pre.find(prog);
    return location->second;
  }

  Node getTransPost(Node prog) const {
    std::map<Node, Node>::const_iterator location = d_trans_post.find(prog);
    return location->second;
  }
  // get template for program prog. This returns a term of the form t[x] where x is the template argument (see below)
  Node getTemplate(Node prog) const {
    std::map<Node, Node>::const_iterator tmpl = d_templ.find(prog);
    if( tmpl!=d_templ.end() ){
      return tmpl->second;
    }else{
      return Node::null();
    }
  }
  // get the template argument for program prog.
  // This is a variable which indicates the position of the function/predicate to synthesize.
  Node getTemplateArg(Node prog) const {
    std::map<Node, Node>::const_iterator tmpla = d_templ_arg.find(prog);
    if( tmpla != d_templ_arg.end() ){
      return tmpla->second;
    }else{
      return Node::null();
    }
  }

 private:
  /** solve trivial
   *
   * If this method returns true, it sets d_isSolved to true and adds
   * t1 ... tn to d_inst if it can be shown that (forall x1 ... xn. P) is
   * unsatisfiable for instantiation {x1 -> t1 ... xn -> tn}.
   */
  bool solveTrivial(Node q);
};

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif

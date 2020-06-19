/*********************                                                        */
/*! \file sygus_eval_unfold.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_eval_unfold
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/sygus/sygus_invariance.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/** SygusEvalUnfold
 *
 * This class implements techniques for eagerly unfolding sygus evaluation
 * functions. For example, given sygus datatype type corresponding to grammar:
 *   A -> 0 | 1 | A+A
 * whose evaluation function is eval, this class adds lemmas that "eagerly
 * unfold" applications of eval based on the model values of evaluation heads
 * in refinement lemmas.
 */
class SygusEvalUnfold
{
 public:
  SygusEvalUnfold(TermDbSygus* tds);
  ~SygusEvalUnfold() {}
  /** register evaluation term
   *
   * This is called by TermDatabase, during standard effort calls when a term
   * n is registered as an equivalence class in the master equality engine.
   * If this term is of the form:
   *   eval( a, t1, ..., tn )
   * where a is a symbolic term of sygus datatype type (not a application of a
   * constructor), then we remember that n is an evaluation function application
   * for evaluation head a.
   */
  void registerEvalTerm(Node n);
  /** register model value
   *
   * This notifies this class that the model value M(a) of an anchor term a is
   * currently v. Assume in the following that the top symbol of v is some sygus
   * datatype constructor C_op.
   *
   * If we have registered terms eval( a, T1 ), ..., eval( a, Tm ), then we
   * ensure that for each i=1,...,m, a lemma of one of the two forms is
   * generated:
   * [A] a=v => eval( a, Ti ) = [[unfold( eval( v, Ti ) )]]
   * [B] is-C_op(v) => eval(a, Ti ) = op(eval( a.1, Ti ), ..., eval( a.k, Ti )),
   * where this corresponds to a "one step folding" of the sygus evaluation
   * function, i.e. op is a builtin operator encoded by constructor C_op.
   *
   * We decide which kind of lemma to send ([A] or [B]) based on the symbol
   * C_op. If op is an ITE, or if C_op is a Boolean operator, then we add [B].
   * Otherwise, we add [A]. The intuition of why [B] is better than [A] for the
   * former is that evaluation unfolding can lead to useful conflict analysis.
   *
   * For each lemma C => eval( a, T ) = T' we infer is necessary, we add C to
   * exps, eval( a, T ) to terms, and T' to vals. The caller should send the
   * corresponding lemma on the output channel.
   *
   * We do the above scheme *for each* selector chain (see d_subterms below)
   * applied to a.
   */
  void registerModelValue(Node a,
                          Node v,
                          std::vector<Node>& exps,
                          std::vector<Node>& terms,
                          std::vector<Node>& vals);
  /** unfold
   *
   * This method is called when a sygus term d (typically a variable for a SyGuS
   * enumerator) has a model value specified by the map vtm. The argument en
   * is an application of kind DT_SYGUS_EVAL, i.e. eval( d, c1, ..., cm ).
   * Typically, d is a shared selector chain, although it may also be a
   * non-constant application of a constructor.
   *
   * If doRec is false, this method returns the one-step unfolding of this
   * evaluation function application. An example of a one step unfolding is:
   *    eval( C_+( d1, d2 ), t ) ---> +( eval( d1, t ), eval( d2, t ) )
   *
   * This function does this unfolding for a (possibly symbolic) evaluation
   * head, where the argument "variable to model" vtm stores the model value of
   * variables from this head. This allows us to track an explanation of the
   * unfolding in the vector exp when track_exp is true.
   *
   * For example, if vtm[d] = C_+( C_x(), C_0() ) and track_exp is true, then
   * this method applied to eval( d, t ) will return
   * +( eval( d.0, t ), eval( d.1, t ) ), and is-C_+( d ) is added to exp.
   *
   * If the argument doRec is true, we do a multi-step unfolding instead of
   * a single-step unfolding. For example, if vtm[d] = C_+( C_x(), C_0() ),
   * then this method applied to eval(d,5) will return 5+0 = 0.
   *
   * Furthermore, notice that any-constant constructors are *never* expanded to
   * their concrete model values. This means that the multi-step unfolding when
   * vtm[d] = C_+( C_x(), any_constant(n) ), then this method applied to
   * eval(d,5) will return 5 + d.2.1, where the latter term is a shared selector
   * chain. In other words, this unfolding elaborates the connection between
   * the builtin integer field d.2.1 of d and the builtin interpretation of
   * this sygus term, for the given argument.
   */
  Node unfold(Node en,
              std::map<Node, Node>& vtm,
              std::vector<Node>& exp,
              bool track_exp = true,
              bool doRec = false);
  /**
   * Same as above, but without explanation tracking. This is used for concrete
   * evaluation heads
   */
  Node unfold(Node en);

 private:
  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;
  /** the set of evaluation terms we have already processed */
  std::unordered_set<Node, NodeHashFunction> d_eval_processed;
  /** map from evaluation heads to evaluation function applications */
  std::map<Node, std::vector<Node> > d_evals;
  /**
   * Map from evaluation function applications to their arguments (minus the
   * evaluation head). For example, eval(x,0,1) is mapped to { 0, 1 }.
   */
  std::map<Node, std::vector<std::vector<Node> > > d_eval_args;
  /**
   * For each (a,M(a)) pair, the number of terms in d_evals that we have added
   * lemmas for
   */
  std::map<Node, std::map<Node, unsigned> > d_node_mv_args_proc;
  /** subterms map
   *
   * This maps anchor terms to the set of shared selector chains with
   * them as an anchor, for example x may map to { x, x.1, x.2, x.1.1 }.
   */
  std::map<Node, std::unordered_set<Node, NodeHashFunction> > d_subterms;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H */

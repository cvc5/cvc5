/*********************                                                        */
/*! \file output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Customized output channel for the theory of strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__OUTPUT_CHANNEL_H
#define CVC4__THEORY__STRINGS__OUTPUT_CHANNEL_H

#include "theory/uf/equality_engine.h"
#include "context/cdlist.h"

#include <climits>
#include <deque>

namespace CVC4 {
namespace theory {
namespace strings {
  
class TheoryStrings;

class OutputChannelStrings {
  typedef context::CDList<Node> NodeList;
 public:
  OutputChannelStrings(TheoryStrings& p, context::Context* c, context::UserContext* u,eq::EqualityEngine& ee,
                       OutputChannel& out);
  ~OutputChannelStrings() {}

  /** send internal inferences
   *
   * This is called when we have inferred exp => conc, where exp is a set
   * of equalities and disequalities that hold in the current equality engine.
   * This method adds equalities and disequalities ~( s = t ) via
   * sendInference such that both s and t are either constants or terms
   * that already occur in the equality engine, and ~( s = t ) is a consequence
   * of conc. This function can be seen as a "conservative" version of
   * sendInference below in that it does not introduce any new non-constant
   * terms to the state.
   *
   * The argument c is a string identifying the reason for the inference.
   * This string is used for debugging purposes.
   *
   * Return true if the inference is complete, in the sense that we infer
   * inferences that are equivalent to conc. This returns false e.g. if conc
   * (or one of its conjuncts if it is a conjunction) was not inferred due
   * to the criteria mentioned above.
   */
  bool sendInternalInference(std::vector<Node>& exp, Node conc, const char* c);
  /** send inference
   *
   * This function should be called when ( exp ^ exp_n ) => eq. The set exp
   * contains literals that are explainable by this class, i.e. those that
   * hold in the equality engine of this class. On the other hand, the set
   * exp_n ("explanations new") contain nodes that are not explainable by this
   * class. This method may call sendInfer or sendLemma. Overall, the result
   * of this method is one of the following:
   *
   * [1] (No-op) Do nothing if eq is true,
   *
   * [2] (Infer) Indicate that eq should be added to the equality engine of this
   * class with explanation EXPLAIN(exp), where EXPLAIN returns the
   * explanation of the node in exp in terms of the literals asserted to this
   * class,
   *
   * [3] (Lemma) Indicate that the lemma ( EXPLAIN(exp) ^ exp_n ) => eq should
   * be sent on the output channel of this class, or
   *
   * [4] (Conflict) Immediately report a conflict EXPLAIN(exp) on the output
   * channel of this class.
   *
   * Determining which case to apply depends on the form of eq and whether
   * exp_n is empty. In particular, lemmas must be used whenever exp_n is
   * non-empty, conflicts are used when exp_n is empty and eq is false.
   *
   * The argument c is a string identifying the reason for inference, used for
   * debugging.
   *
   * If the flag asLemma is true, then this method will send a lemma instead
   * of an inference whenever applicable.
   */
  void sendInference(std::vector<Node>& exp,
                     std::vector<Node>& exp_n,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  /** same as above, but where exp_n is empty */
  void sendInference(std::vector<Node>& exp,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  /** Send phase requirement
   * 
   * This method is called to indicate this class should send a phase
   * requirement request to the output channel for literal lit to be
   * decided with polarity pol.
   */
  void sendPhaseRequirement(Node lit, bool pol) const;
  
  // FIXME
  /** Do pending facts
   * 
   * This method asserts pending facts stored in d_pending to the equality
   * engine.
   */
  void doPendingFacts();
  void doPendingLemmas();
  /** 
   * Have we processed an inference during this call to check? In particular,
   * this returns true if we have a pending fact or lemma, or have encountered
   * a conflict.
   */
  inline bool hasProcessed() const;
  /** Do we have a pending fact to add to the equality engine? */
  inline bool hasPendingFact() const;
  /** Do we have a pending lemma to send on the output channel? */
  inline bool hasPendingLemma() const;
  /** Are we in conflict? */
  inline bool hasConflict() const;
 protected:
  /**
   * Indicates that ant => conc should be sent on the output channel of this
   * class. This will either trigger an immediate call to the conflict
   * method of the output channel of this class of conc is false, or adds the
   * above lemma to the lemma cache d_lemma_cache, which may be flushed
   * later within the current call to TheoryStrings::check.
   *
   * The argument c is a string identifying the reason for inference, used for
   * debugging.
   */
  void sendLemma(Node ant, Node conc, const char* c);
  /**
   * Indicates that conc should be added to the equality engine of this class
   * with explanation eq_exp. It must be the case that eq_exp is a (conjunction
   * of) literals that each are explainable, i.e. they already hold in the
   * equality engine of this class.
   */
  void sendInfer(Node eq_exp, Node eq, const char* c);
  bool sendSplit(Node a, Node b, const char* c, bool preq = true);
private:
  /** the parent theory of strings object */
  TheoryStrings& d_parent;
  /** the equality engine
   * 
   * This is a reference to the equality engine of the theory of strings.
   */
  eq::EqualityEngine& d_ee;
  /** the output channel 
   * 
   * This is a reference to the output channel of the theory of strings.
   */
  OutputChannel& d_out;

  // FIXME
  //list of pairs of nodes to merge
  std::map< Node, Node > d_pending_exp;
  std::vector< Node > d_pending;
  std::map< Node, bool > d_pending_req_phase;
  
  // FIXME
  std::vector< Node > d_lemma_cache;
  
  // FIXME
  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList d_infer;
  NodeList d_infer_exp;
  
  /** Common constants */
  Node d_true;
  Node d_false;
  //--------------------------- equality engine
  /**
   * Get the representative of t in the equality engine of this class, or t
   * itself if it is not registered as a term.
   */
  Node getRepresentative(Node t);
  /** Is t registered as a term in the equality engine of this class? */
  bool hasTerm(Node a);
  /**
   * Are a and b equal according to the equality engine of this class? Also
   * returns true if a and b are identical.
   */
  bool areEqual(Node a, Node b);
  /**
   * Are a and b disequal according to the equality engine of this class? Also
   * returns true if the representative of a and b are distinct constants.
   */
  bool areDisequal(Node a, Node b);
  //--------------------------- end equality engine  
  
  

  /** mkAnd **/
  static Node mkAnd(std::vector<Node>& a);

};/* class TheoryStrings */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_H */

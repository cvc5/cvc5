/*********************                                                        */
/*! \file polymorphic_engine.h
 ** \verbatim
 ** Original author: Francois Bobot
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef __CVC4__POLYMORPHIC_ENGINE_H
#define __CVC4__POLYMORPHIC_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantInfo;

class paralemma {
public:
  Node bv; /** Bound Type Variables */
  Node body; /** Body of the polymorphic lemma */
  Node origlemma; /* given by assert */
  /**  When there are no universal quantifiers, these polymorphic
       constants are used as triggers */
  std::unordered_set<TNode, TNodeHashFunction> polymorphicConstants;

  paralemma(Node lemma);
};

class PolymorphicEngine : public QuantifiersModule
{
  std::vector<paralemma> d_lemma;
  std::unordered_set<TypeNode, TypeNode::HashFunction> d_doneType;
  std::map< TypeNode, unsigned > d_ntermsProcessed;

  /** map of terms that will trigger the addition of instantiated
      polymorphic lemma. For not creating trivial matching loop with
      polymorphic lemma without terms binding.
      (par (a) (= (length (as nil (list a)) 0)))
 */
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> d_csttrigger;

  void instantiate( paralemma& lemma,
                    std::unordered_map<TypeNode, TypeNode, TypeNode::HashFunction>& ty_subst,
                    size_t v_id,
                    bool todo_used,
                    std::unordered_set<TypeNode, TypeNode::HashFunction>& doneType,
                    std::unordered_set<TypeNode, TypeNode::HashFunction>& todoType );

public:
  PolymorphicEngine( context::Context* c, QuantifiersEngine* qe );
  /** Quantifiers Module interface */
  void presolve();
  bool needsCheck(Theory::Effort e);
  void check( Theory::Effort e, unsigned quant_e );
  void registerQuantifier( Node q );
  void assertNode( Node n );
  std::string identify() const { return "PolymorphicEngine"; }

  void newTerm( Node n );
};

}
}
}

#endif

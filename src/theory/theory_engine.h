/*********************                                                        */
/** theory_engine.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include "expr/node.h"
#include "theory/theory.h"
#include "theory/theoryof_table.h"

#include "theory/booleans/theory_bool.h"
#include "theory/uf/theory_uf.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

class SmtEngine;

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Associated SMT engine */
  SmtEngine* d_smt;

  /** A table of Kinds to pointers to Theory */
  theory::TheoryOfTable theoryOfTable;

  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    TheoryEngine* d_engine;
    context::Context* d_context;
    context::CDO<Node> d_conflictNode;

  public:

    EngineOutputChannel(TheoryEngine* engine, context::Context* context)
    : d_engine(engine),
      d_context(context),
      d_conflictNode(context)
    {
    }

    void conflict(TNode conflictNode, bool) throw(theory::Interrupted) {
      Debug("theory") << "EngineOutputChannel::conflict(" << conflictNode << ")" << std::endl;
      d_conflictNode = conflictNode;
      throw theory::Interrupted();
    }

    void propagate(TNode, bool) throw(theory::Interrupted) {
    }

    void lemma(TNode, bool) throw(theory::Interrupted) {
    }

    void explanation(TNode, bool) throw(theory::Interrupted) {
    }
  };

  EngineOutputChannel d_theoryOut;
  theory::booleans::TheoryBool d_bool;
  theory::uf::TheoryUF d_uf;
  theory::arith::TheoryArith d_arith;
  theory::arrays::TheoryArrays d_arrays;
  theory::bv::TheoryBV d_bv;

public:

  /**
   * Construct a theory engine.
   */
  TheoryEngine(SmtEngine* smt, context::Context* ctxt) :
    d_smt(smt),
    d_theoryOut(this, ctxt),
    d_bool(ctxt, d_theoryOut),
    d_uf(ctxt, d_theoryOut),
    d_arith(ctxt, d_theoryOut),
    d_arrays(ctxt, d_theoryOut),
    d_bv(ctxt, d_theoryOut)
  {
    theoryOfTable.registerTheory(&d_bool);
    theoryOfTable.registerTheory(&d_uf);
    theoryOfTable.registerTheory(&d_arith);
    theoryOfTable.registerTheory(&d_arrays);
    theoryOfTable.registerTheory(&d_bv);
  }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  theory::Theory* theoryOf(const TNode& node) {
    if (node.getKind() == kind::EQUAL) return &d_uf;
    else return NULL;
  }

  /**
   * Assert the formula to the apropriate theory.
   * @param node the assertion
   */
  inline void assertFact(const TNode& node) {
    Debug("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;
    theory::Theory* theory = node.getKind() == kind::NOT ? theoryOf(node[0]) : theoryOf(node);
    if (theory != NULL) theory->assertFact(node);
  }

  inline void check(theory::Theory::Effort effort) {
    try {
      d_uf.check(effort);
    } catch (const theory::Interrupted&) {
      Debug("theory") << "TheoryEngine::check() => conflict" << std::endl;
    }
  }

  /**
   * Returns the last conflict (if any).
   */
  inline Node getConflict() {
    return d_theoryOut.d_conflictNode;
  }

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */

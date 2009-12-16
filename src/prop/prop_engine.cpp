/*********************                                           -*- C++ -*-  */
/** prop_engine.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "prop/prop_engine.h"
#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "prop/minisat/mtl/Vec.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "util/Assert.h"
#include "util/output.h"

#include <utility>
#include <map>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {

PropEngine::PropEngine(DecisionEngine& de, TheoryEngine& te) :
  d_de(de), d_te(te), d_sat() {
}

void PropEngine::addVars(Node e) {
  Debug("prop") << "adding vars to " << e << endl;
  for(Node::iterator i = e.begin(); i != e.end(); ++i) {
    Debug("prop") << "expr " << *i << endl;
    if((*i).getKind() == VARIABLE) {
      if(d_vars.find(*i) == d_vars.end()) {
        Var v = d_sat.newVar();
        Debug("prop") << "adding var " << *i << " <--> " << v << endl;
        d_vars.insert(make_pair(*i, v));
        d_varsReverse.insert(make_pair(v, *i));
      } else Debug("prop") << "using var " << *i << " <--> " << d_vars[*i] << endl;
    } else addVars(*i);
  }
}

static void doAtom(SimpSolver* minisat, map<Node, Var>* vars, Node e, vec<Lit>* c) {
  if(e.getKind() == VARIABLE) {
    map<Node, Var>::iterator v = vars->find(e);
    Assert(v != vars->end());
    c->push(Lit(v->second, false));
    return;
  }
  if(e.getKind() == NOT) {
    Assert(e.numChildren() == 1);
    Node child = *e.begin();
    Assert(child.getKind() == VARIABLE);
    map<Node, Var>::iterator v = vars->find(child);
    Assert(v != vars->end());
    c->push(Lit(v->second, true));
    return;
  }
  Unhandled();
}

static void doClause(SimpSolver* minisat, map<Node, Var>* vars, map<Var, Node>* varsReverse, Node e) {
  vec<Lit> c;
  Debug("prop") << "  " << e << endl;
  if(e.getKind() == VARIABLE || e.getKind() == NOT) {
    doAtom(minisat, vars, e, &c);
  } else {
    Assert(e.getKind() == OR);
    for(Node::iterator i = e.begin(); i != e.end(); ++i) {
      Debug("prop") << "    " << *i << endl;
      doAtom(minisat, vars, *i, &c);
    }
  }
  Notice() << "added clause of length " << c.size() << endl;
  for(int i = 0; i < c.size(); ++i)
    Notice() << " " << (sign(c[i]) ? "-" : "") << var(c[i]);
  Notice() << " [[";
  for(int i = 0; i < c.size(); ++i)
    Notice() << " " << (sign(c[i]) ? "-" : "") << (*varsReverse)[var(c[i])];
  Notice() << " ]] " << endl;
  minisat->addClause(c);
}

void PropEngine::solve(Node e) {
  Debug("prop") << "SOLVING " << e << endl;
  addVars(e);
  if(e.getKind() == AND) {
    Debug("prop") << "AND" << endl;
    for(Node::iterator i = e.begin(); i != e.end(); ++i)
      doClause(&d_sat, &d_vars, &d_varsReverse, *i);
  } else doClause(&d_sat, &d_vars, &d_varsReverse, e);

  d_sat.verbosity = 1;
  bool result = d_sat.solve();

  Notice() << "result is " << (result ? "sat" : "unsat") << endl;
  if(result) {
    Notice() << "model:" << endl;
    for(int i = 0; i < d_sat.model.size(); ++i)
      Notice() << " " << toInt(d_sat.model[i]);
    Notice() << endl;
    for(int i = 0; i < d_sat.model.size(); ++i)
      Notice() << " " << d_varsReverse[i] << " is "
               << (d_sat.model[i] == l_False ? "FALSE" :
                   (d_sat.model[i] == l_Undef ? "UNDEF" :
                    "TRUE")) << endl;
  } else {
    Notice() << "conflict:" << endl;
    for(int i = 0; i < d_sat.conflict.size(); ++i)
      Notice() << " " << (sign(d_sat.conflict[i]) ? "-" : "") << var(d_sat.conflict[i]);
    Notice() << " [[";
    for(int i = 0; i < d_sat.conflict.size(); ++i)
      Notice() << " " << (sign(d_sat.conflict[i]) ? "-" : "") << d_varsReverse[var(d_sat.conflict[i])];
    Notice() << " ]] " << endl;
  }
}

}/* CVC4 namespace */

/*********************                                           -*- C++ -*-  */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
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
  d_de(de), d_te(te) {
}

void PropEngine::addVars(SimpSolver* minisat, map<Node, Var>* vars, map<Var, Node>* varsReverse, Node e) {
  Debug("prop") << "adding vars to " << e << endl;
  for(Node::iterator i = e.begin(); i != e.end(); ++i) {
    Debug("prop") << "expr " << *i << endl;
    if((*i).getKind() == VARIABLE) {
      if(vars->find(*i) == vars->end()) {
        Var v = minisat->newVar();
        Debug("prop") << "adding var " << *i << " <--> " << v << endl;
        (*vars).insert(make_pair(*i, v));
        (*varsReverse).insert(make_pair(v, *i));
      } else Debug("prop") << "using var " << *i << " <--> " << (*vars)[*i] << endl;
    } else addVars(minisat, vars, varsReverse, *i);
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
    Assert(e.getNumChildren() == 1);
    Node child = *e.begin();
    Assert(child.getKind() == VARIABLE);
    map<Node, Var>::iterator v = vars->find(child);
    Assert(v != vars->end());
    c->push(Lit(v->second, true));
    return;
  }
  if(e.getKind() == OR) {
    for(Node::iterator i = e.begin(); i != e.end(); ++i) {
      doAtom(minisat, vars, *i, c);
    }
    return;
  }
  Unhandled(e.getKind());
}

static void doClause(SimpSolver* minisat, map<Node, Var>* vars, map<Var, Node>* varsReverse, Node e) {
  vec<Lit> c;
  Debug("prop") << "  " << e << endl;
  if(e.getKind() == VARIABLE || e.getKind() == NOT) {
    doAtom(minisat, vars, e, &c);
  } else if(e.getKind() == FALSE) {
    // inconsistency
    Notice() << "adding FALSE clause" << endl;
    Var v = minisat->newVar();
    c.push(Lit(v, true));
    minisat->addClause(c);
    Notice() << "added unit clause " << v << " [[ " << (*varsReverse)[v] << " ]]" << endl;
    c.clear();
    c.push(Lit(v, false));
    minisat->addClause(c);
    Notice() << "added unit clause -" << v << " [[ -" << (*varsReverse)[v] << " ]]" << endl;
  } else if(e.getKind() == TRUE) {
    Notice() << "adding TRUE clause (do nothing)" << endl;
    // do nothing
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
  // FIXME: when context mgr comes online, keep the solver around
  // between solve() calls if we can
  CVC4::prop::minisat::SimpSolver sat;
  std::map<Node, CVC4::prop::minisat::Var> vars;
  std::map<CVC4::prop::minisat::Var, Node> varsReverse;

  Debug("prop") << "SOLVING " << e << endl;
  addVars(&sat, &vars, &varsReverse, e);
  if(e.getKind() == AND) {
    Debug("prop") << "AND" << endl;
    for(Node::iterator i = e.begin(); i != e.end(); ++i)
      doClause(&sat, &vars, &varsReverse, *i);
  } else doClause(&sat, &vars, &varsReverse, e);

  sat.verbosity = 1;
  bool result = sat.solve();

  Notice() << "result is " << (result ? "sat/invalid" : "unsat/valid") << endl;
  if(result) {
    Notice() << "model:" << endl;
    for(int i = 0; i < sat.model.size(); ++i)
      Notice() << " " << toInt(sat.model[i]);
    Notice() << endl;
    for(int i = 0; i < sat.model.size(); ++i)
      Notice() << " " << varsReverse[i] << " is "
               << (sat.model[i] == l_False ? "FALSE" :
                   (sat.model[i] == l_Undef ? "UNDEF" :
                    "TRUE")) << endl;
  } else {
    Notice() << "conflict:" << endl;
    for(int i = 0; i < sat.conflict.size(); ++i)
      Notice() << " " << (sign(sat.conflict[i]) ? "-" : "") << var(sat.conflict[i]);
    Notice() << " [[";
    for(int i = 0; i < sat.conflict.size(); ++i)
      Notice() << " " << (sign(sat.conflict[i]) ? "-" : "") << varsReverse[var(sat.conflict[i])];
    Notice() << " ]] " << endl;
  }
}

}/* CVC4 namespace */

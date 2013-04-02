/*********************                                                        */
/*! \file theory_bv_white.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include <cxxtest/TestSuite.h>

#include "theory/theory.h"
#include "theory/bv/bitblaster.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "context/context.h"

#include "theory/theory_test_utils.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils; 
using namespace CVC4::expr;
using namespace CVC4::context;

using namespace std;

class TheoryBVWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

  bool debug;

public:

  TheoryBVWhite() : debug(false) {}


  void setUp() {
    // d_ctxt = new Context();
    // d_nm = new NodeManager(d_ctxt, NULL);
    // d_scope = new NodeManagerScope(d_nm);

  }

  void tearDown() {
    // delete d_scope;
    // delete d_nm;
    // delete d_ctxt;
  }

 
  void testBitblasterCore() {
    // ClauseManager tests 
    // Context* ctx = new Context();
    // Bitblaster* bb = new Bitblaster(ctx); 
    
    // NodeManager* nm = NodeManager::currentNM();
    // TODO: update this
    // Node a = nm->mkVar("a", nm->mkBitVectorType(4));
    // Node b = nm->mkVar("b", nm->mkBitVectorType(4));
    // Node a1 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(2,1)), a);
    // Node b1 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(2,1)), b);
    
    // Node abeq = nm->mkNode(kind::EQUAL, a, b);
    // Node neq = nm->mkNode(kind::NOT, abeq);
    // Node a1b1eq = nm->mkNode(kind::EQUAL, a1, b1);
    
    // bb->bitblast(neq);
    // bb->bitblast(a1b1eq); 

    // /// constructing the rest of the problem 
    // Node a2 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(0,0)), a);
    // Node b2 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(0,0)), b);
    // Node eq2 = nm->mkNode(kind::EQUAL, a2, b2); 
    
    // Node a3 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(3,3)), a);
    // Node b3 = nm->mkNode(nm->mkConst<BitVectorExtract>(BitVectorExtract(3,3)), b);
    // Node eq3 = nm->mkNode(kind::EQUAL, a3, b3);

    // bb->bitblast(eq2);
    // bb->bitblast(eq3); 

    // ctx->push();
    // bb->assertToSat(neq);
    // bb->assertToSat(a1b1eq);
    // bool res = bb->solve();
    // TS_ASSERT (res == true);

    // ctx->push();
    // bb->assertToSat(eq2);
    // bb->assertToSat(eq3); 

    // res = bb->solve();
    // TS_ASSERT(res == false); 
    
    //delete bb;    
    
  }

};

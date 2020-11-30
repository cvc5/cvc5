; SCRUBBER: sed -e 's/unsat.*/unsat/'
; EXPECT: unsat
; EXIT: 0
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(declare-fun v0 () (_ BitVec 16))
(declare-fun v1 () (_ BitVec 16))
(declare-fun v2 () (_ BitVec 16))
(declare-fun v3 () (_ BitVec 16))
(declare-fun v4 () (_ BitVec 16))
(declare-fun v5 () (_ BitVec 16))
(assert (and
	 (bvult v2 v4)
	 (bvult v3 v4)
	 (bvult v0 v1)
	 (bvult v1 v2)
	 (bvult v1 v3)
	 (bvult v4 v5)
	 (bvult v5 v1)
	 ))
(check-sat)
(exit)

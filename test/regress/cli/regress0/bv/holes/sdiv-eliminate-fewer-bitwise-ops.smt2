; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	(bvsdiv x y)
	(ite (xor (bvuge x #b10000) (bvuge y #b10000))
		(bvneg (bvudiv (ite (bvuge x #b10000) (bvneg x) x) (ite (bvuge y #b10000) (bvneg y) y)))
		(bvudiv (ite (bvuge x #b10000) (bvneg x) x) (ite (bvuge y #b10000) (bvneg y) y)))
	)))
(check-sat)
(exit)

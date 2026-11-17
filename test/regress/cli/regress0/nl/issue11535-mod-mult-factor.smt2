; EXPECT: unsat
(set-logic QF_NIA)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (> c 0))
(assert (not
	 (= (mod (* a c b) c)
	    0)))

(check-sat)
(exit)

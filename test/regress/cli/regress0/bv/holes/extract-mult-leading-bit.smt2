; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 25))
(declare-const y (_ BitVec 25))
(assert (not (=
	; Top 5 bits
	((_ extract 64 60) (bvmul
		; 40 zeros on top
		(concat #b0000000000000000000000000000000000000000 x)
		(concat #b0000000000000000000000000000000000000000 y)
	))
	; Should be all 0
	#b00000
	)))
(check-sat)
(exit)

; EXPECT: unsat
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x1 () (_ BitVec 10))
(declare-fun x2 () (_ BitVec 10))
(declare-fun x3 () (_ BitVec 10))
;(assert (not (=
;	((_ extract 14 5) (concat x2 x1))
;	(concat
;		((_ extract 4 0) x2)
;		((_ extract 9 5) x1)
;	)
;	)))
(assert (not (=
	((_ extract 24 5) (concat x3 x2 x1))
	(concat
		((_ extract 4 0) x3)
		((_ extract 9 0) x2)
		((_ extract 9 5) x1)
	)
	)))
(check-sat)
(exit)

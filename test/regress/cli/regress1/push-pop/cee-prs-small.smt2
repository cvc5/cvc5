; COMMAND-LINE: -i --ee-mode=distributed
; COMMAND-LINE: -i --ee-mode=central
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((r 0)) (((r_ctor (x Int)))))
(declare-datatype tup ((mkt (t1 (Array Int Int)) (t2 (Array Int Int)))))
(declare-datatypes ((q 0)) (((R (x (Array Int r)) (y tup)))))
(declare-fun z () q)
(assert (not (= 1 (select (t2 (y z)) 1))))
(assert (= z (R ((as const (Array Int r)) (r_ctor 0)) (mkt ((as const (Array Int Int)) 1) ((as const (Array Int Int)) 0)))))
(check-sat)
(assert (= (x (select (x z) 0)) (select (t1 (y z)) 1)))
(check-sat)

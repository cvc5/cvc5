; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat

(set-logic QF_LIA)
(declare-fun _b () Int)
(declare-fun _n () Int)
(declare-fun _x () Bool)

(assert (<= 2 _n))
(assert  (not (= _b 0)))

(push 1)
(assert (or (= _n 1) (or _x (= _b 0))))
(check-sat)
(pop 1)

(assert (or (= _n 1) (or _x (= _b 0))))

(assert (or (not _x) (= _n 1)))

(check-sat)

; COMMAND-LINE: --incremental --simplification=none
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_UFLIA)
(declare-fun base () Int)
(declare-fun n () Int)

(declare-fun g (Int) Bool)
(declare-fun f (Int) Bool)

(push 1)
(assert (<= 0 n))
(assert (f n))
(assert (= (f n) (or (= (- n base) 1) (g n))))
(check-sat)
(pop 1)

(push 1)
(assert (<= 0 n))

(assert (or (= (- n base) 1) (g n)))
(assert (not (g n)))
(assert (= base (- 2)))

(check-sat)
(pop 1)


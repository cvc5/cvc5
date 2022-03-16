; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat

(set-logic QF_UFLIA)
(declare-fun b () Int)
(declare-fun n () Int)
(declare-fun f (Int) Bool)
(declare-fun g (Int) Bool)

(assert (<= 0 n))
(push 1)

(assert (or (g (- 1)) (= b 0)))

(assert (or (= (- n b) 1) (not (or (= (- n b) 1) (f (- n 2))))))

(check-sat)
(pop 1)

(push 1)
(assert (or (g  (- n 1)) (= n b)))
(assert (or (not (f n)) (not (= n b))))

(assert (not (f (- n 2))))


(assert (or (not (g (- n 1))) (not (= (- n b) 1))))

(assert (or (not (g (- n 1))) (or (= (- n b) 1) (f (- n 2)))))



(assert (or (f n) (and (not (f n)) (f n))))

(check-sat)
(pop 1)
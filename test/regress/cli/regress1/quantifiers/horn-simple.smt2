; COMMAND-LINE: --sygus-unif-pi=complete --sygus-infer
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-fun I (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I x))))

(assert (forall ((x Int)) (=> (and (I x) (< x 6)) (I (+ x 1)))))

(assert (forall ((x Int)) (=> (I x) (<= x 10))))

(check-sat)

; EXPECT: sat
(set-logic QF_UFNRA)
(declare-const x Bool)
(declare-fun x2 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun g (Bool Real Real) Real)
(assert (and (> x6 0) (or x (= x5 (* x2 (/ 1 2)))) (or x (= x2 (* 1.0 (g false (g false (/ 1 x6) x6) x2))))))
(check-sat)

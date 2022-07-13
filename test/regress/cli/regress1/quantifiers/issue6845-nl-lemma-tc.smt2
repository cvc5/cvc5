; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic NIRA)
(declare-const x Bool)
(declare-fun i () Int)
(declare-fun i1 () Int)
(assert (< 1.0 (to_real i)))
(assert (distinct 0.0 (/ 7.0 (to_real i))))
(push)
(assert (or (exists ((q Int)) (= 0 (* i i1)))))
(check-sat)
(pop)
(assert (or (= i1 1) x))
(check-sat)

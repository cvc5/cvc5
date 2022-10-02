; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALIRA)
(declare-const x Real)
(declare-fun i () Int)
(declare-fun i1 () Int)
(push)
(assert (< 1 (- i)))
(check-sat)
(pop)
(push)
(assert (or (>= i1 (* 5 (- i)))))
(check-sat)
(pop)
(assert (or (> i1 1) (= x (to_real i))))
(check-sat)
(assert (not (is_int x)))
(check-sat)

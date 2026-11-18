; EXPECT: sat
(set-logic ALL)
(set-option :check-models true)
(declare-fun a () Real)
(define-fun b () Real 1.0)
(declare-fun c () Real)
(assert (and (> b 0.0) (= 0.0 (* b (+ 1.0 (* a a c a))))))
(check-sat)

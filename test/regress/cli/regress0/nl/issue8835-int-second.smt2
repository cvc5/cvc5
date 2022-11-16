; EXPECT: sat
; REQUIRES: poly
(set-logic ALL)
(set-option :nl-cov true)
(set-option :check-models true)
(declare-fun a () Int) 
(declare-fun b () Int) 
(declare-fun c () Real) 
(assert (= (* 1 (/ 1 69)) (+ b 1 (* b (* (* 2 c) a)) (- 1)))) 
(check-sat)

; REQUIRES: poly
; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :nl-cov true)                                                       
(declare-fun a () Int)                                                          
(declare-fun b () Int)                                                          
(declare-fun c () Real)                                                         
(assert (= (* 1 (/ c (/ 1 69))) (+ b 1 (* (+ 69 69) (- (* (* (+ 69 (+ b 1          
(* (mod (- 1) b) (to_int c)) (abs (* (* 2 c) a)))) c) a))) (+ 2 69))))          
(check-sat)       

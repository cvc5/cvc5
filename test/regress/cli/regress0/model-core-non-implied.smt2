; COMMAND-LINE: --produce-models --model-cores=non-implied
; SCRUBBER: sed 's/(define-fun.*/define-fun/g'
; EXPECT: sat
; EXPECT: (
; EXPECT: define-fun
; EXPECT: )
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(assert (and (= x y) (= y z) (= y w) (= (+ u 1) w)))
; a single value for a variable implies the others
(check-sat)
(get-model)

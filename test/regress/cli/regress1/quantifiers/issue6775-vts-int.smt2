; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic NIA)
(declare-const x43799 Bool)
(declare-const x32 Bool)
(declare-fun v11 () Bool)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i () Int)
(assert (or (< 0 i2) (not x32) (not v11)))
(assert (or x32 (exists ((q Int)) (not (= x32 (> q (abs i3)))))))
(assert (< i2 i))
(check-sat)
(assert (or (not v11) x43799))
(assert (= (+ 3 i (* 13 4 5 (abs i3))) (* 157 4 (- 1) (+ 1 1 i2 i))))
(check-sat)

; check-models disabled due to intermediate terms from sygus-inst

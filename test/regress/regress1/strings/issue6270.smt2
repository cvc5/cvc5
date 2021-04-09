; COMMAND-LINE: --strings-exp --nl-ext-tplanes
; EXPECT: unsat
(set-logic ALL)
(declare-fun i9 () Int)
(declare-fun str0 () String)
(declare-fun str9 () String)
(assert (and (= 0 (str.indexof str9 str9 (abs (str.len str0)))) (= (abs (str.len str0)) (+ (- 5) (* i9 i9)))))
(check-sat)

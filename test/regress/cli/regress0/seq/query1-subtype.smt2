; COMMAND-LINE: --strings-exp --simplification=none
; EXPECT: sat
(set-logic ALL)
(declare-fun x () (Seq Real))
(declare-fun y () (Seq Real))
(declare-fun a () Real)
(declare-fun b () Real)
(assert
(and (= x (seq.unit b)) (= x (str.update y 2 y)) (= x (str.update y 1 x)) (= x (seq.unit 1.0)) (= x (str.update y 1 (as seq.empty (Seq Real)))))
)
(check-sat)

; COMMAND-LINE: --strings-exp --simplification=none --strings-fmf
; EXPECT: sat
(set-logic ALL)
(declare-fun x () (Seq Real))
(declare-fun y () (Seq Real))
(declare-fun a () Real)
(declare-fun b () Real)
(assert
(and (not (= (= x (str.update x 2 (seq.unit 1.0))) (= x (str.update x 2 (str.update x 0 y))))) (not (= b (seq.nth x 2))))
)
(check-sat)

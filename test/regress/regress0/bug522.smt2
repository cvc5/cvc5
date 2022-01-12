; EXPECT: sat
; EXPECT: sat
(set-option :incremental true)
(set-logic QF_UF)

(push 1)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(assert (= x y))
(check-sat)
(pop 1)

(check-sat)

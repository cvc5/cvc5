; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun a () U)
(declare-fun b () U)

(assert (not (sep (not (pto x a)) (pto y b))))
(check-sat)

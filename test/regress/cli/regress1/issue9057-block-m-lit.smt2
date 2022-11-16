; COMMAND-LINE: --produce-models
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Int)
(assert (not (ite (= a 0) true false)))
(check-sat)
(block-model :literals)

; COMMAND-LINE: --check-models --check-unsat-cores --sygus-inst
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (_ BitVec 2))
(assert (= #b01 (select (store (store a #b01 (bvadd #b01 (select a #b00))) #b10 #b00) b)))
(check-sat)

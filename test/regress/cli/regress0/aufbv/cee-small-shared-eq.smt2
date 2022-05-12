; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 16)))
(assert (not (= (_ bv0 16) (select a ((_ extract 14 14) (select a (_ bv0 1)))))))
(check-sat)

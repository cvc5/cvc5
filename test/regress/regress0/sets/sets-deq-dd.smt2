; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Set (_ BitVec 1)))
(assert (not (= S (as emptyset (Set (_ BitVec 1))))))
(check-sat)

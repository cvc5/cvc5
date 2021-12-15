; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun S () (Bag (_ BitVec 1)))
(assert (not (= S (as bag.empty (Bag (_ BitVec 1))))))
(check-sat)

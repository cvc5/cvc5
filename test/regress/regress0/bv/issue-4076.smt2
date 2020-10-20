; COMMAND-LINE: --incremental
; COMMAND-LINE: --incremental --bv-solver=simple
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun a ((_ BitVec 2)) Int)
(declare-fun b (Int) (_ BitVec 2))
(declare-const c Int)
(declare-const d Int)
(assert (= (a #b01) 1))
(assert(= 0 (a (bvlshr (b c) (b d)))))
(push)
(check-sat)
(pop)
(check-sat)

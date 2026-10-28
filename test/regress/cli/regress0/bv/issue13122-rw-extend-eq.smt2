; COMMAND-LINE: --bv-rw-extend-eq
; EXPECT: sat
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= (bvadd x y) (bvmul x y)))
(check-sat)

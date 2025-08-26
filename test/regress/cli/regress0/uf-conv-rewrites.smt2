; COMMAND-LINE: --eager-arith-bv-conv
; EXPECT: unsat
(set-logic ALL)

(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 5))


(assert (or

(not (= ((_ int_to_bv 4) (ubv_to_int x)) (concat #b0 x)))
(not (= ((_ int_to_bv 4) (ubv_to_int y)) ((_ extract 3 0) y)))

(not (= (ubv_to_int x) (ubv_to_int (concat #b0 x))))

))

(check-sat)

; COMMAND-LINE: --eager-arith-bv-conv
; EXPECT: unsat
(set-logic ALL)

(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 5))


(assert (or

(not (= ((_ int2bv 4) (bv2nat x)) (concat #b0 x)))
(not (= ((_ int2bv 4) (bv2nat y)) ((_ extract 3 0) y)))

(not (= (bv2nat x) (bv2nat (concat #b0 x))))

))

(check-sat)

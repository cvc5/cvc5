; COMMAND-LINE: --no-bv-div-zero-const --no-check-unsat-cores
; COMMAND-LINE: --bv-solver=simple --no-bv-div-zero-const --no-check-unsat-cores
(set-logic QF_BV)
(set-info :status sat)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (not (= (bvugt (bvurem y x) x) (ite (= x #x0) (bvugt y #x0) false))))
(check-sat)

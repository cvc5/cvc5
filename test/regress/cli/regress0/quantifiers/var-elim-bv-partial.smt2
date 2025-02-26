; COMMAND-LINE:
; COMMAND-LINE: --var-ent-eq-elim-quant
; EXPECT: unsat
(set-logic ALL)
(declare-const y (_ BitVec 16))
(declare-const z (_ BitVec 32))
(declare-fun P ((_ BitVec 16)) Bool)
(assert (forall ((x (_ BitVec 16))) (=> (= (concat x y) z) (P x))))
(assert (not (P ((_ extract 31 16) z))))
(assert (= y ((_ extract 15 0) z)))
(check-sat)

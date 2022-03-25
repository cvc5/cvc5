(set-logic UFC)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)

(assert (not (_ fmf.card U 2)))

(assert (forall ((x U)) (or (= x a) (= x b))))

(check-sat)

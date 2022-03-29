(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)

(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)

(assert (= (not (= (f a) d)) (not (= d (f b)))))

(assert (or (not (= (f a) d)) (not (= d (f b)))))
(assert (or (= (f a) d) (= d (f b))))

(check-sat)

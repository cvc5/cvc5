(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-const w Int)
(declare-const w1 Int)
(declare-const w2 Int)

;------- f -------
(assert (= w1 (as sep.nil Int)))
(assert (= w2 (as sep.nil Int)))
;-----------------

(assert (pto w (as sep.nil Int)))
(assert (not (and (sep (and (emp 0 0) (= w2 (as sep.nil Int))) (pto w w1)) (sep (pto w w2) true))))

(check-sat)
;(get-model)

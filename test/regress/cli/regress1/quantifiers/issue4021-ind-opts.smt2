; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic HO_ALL)
(set-option :miniscope-quant agg)
(set-option :conjecture-gen true)
(set-option :int-wf-ind true)
(set-option :sygus-inference true)
(set-info :status unsat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun e () Real)
(assert (forall ((d Real)) (and (or (< (/ (* (- a) d) 0.0) c) (> b 0.0)) (= (= d 0.0) (= e 0.0)))))
(check-sat)

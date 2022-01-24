(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_h:A. a_h + |UNIVERALSET| - n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_h () Int)

(assert (<= a_h n))
(assert (>= a_h 0))
(assert (>= a_h (- n t)))


(assert (and (< (- (+ a_h (bag.card UNIVERALSET)) n) 1) (> 1 0)))

(check-sat)

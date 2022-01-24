(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_fi:A. 3a_fi + |UNIVERALSET| - 3n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_fi () Int)

(assert (<= a_fi n))
(assert (>= a_fi 0))
(assert (>= a_fi (- n t)))


(assert (and (< (- (+ (* 3 a_fi) (bag.card UNIVERALSET)) (* 3 n)) 1) (> 1 0)))

(check-sat)

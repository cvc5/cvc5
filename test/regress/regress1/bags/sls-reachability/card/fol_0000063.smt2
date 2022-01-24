(set-logic ALL)

(set-option :fmf-bound true)

(set-info :status unsat)

; C(~f)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))


(assert
 (not (>= (* 2 (bag.card (bag.difference_subtract UNIVERALSET f))) (+ (- n t) 1))))

(check-sat)

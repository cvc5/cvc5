(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_fh:A. 2a_fh + |~f| - 2n >= 1 or 1 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_fh () Int)

(assert (<= a_fh n))
(assert (>= a_fh 0))
(assert (>= a_fh (- n t)))


(assert
 (and
  (< (- (+ (* 2 a_fh) (bag.card (bag.difference_subtract UNIVERALSET f))) (* 2 n)) 1)
  (> 1 0)))

(check-sat)

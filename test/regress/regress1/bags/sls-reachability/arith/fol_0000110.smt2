(set-logic ALL)

(set-option :fmf-bound true)


(set-info :status unsat)

; forall a_ev:A. a_ev + |~f| - n >= (n - t + 1) / 2 or (n - t + 1) / 2 <= 0

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun f () (Bag Int))
(declare-fun UNIVERALSET () (Bag Int))

(assert (bag.subbag f UNIVERALSET))
(assert (= (bag.card UNIVERALSET) n))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (<= (bag.card f) t))

(declare-fun a_ev () Int)

(assert (<= a_ev n))
(assert (>= a_ev 0))
(assert (>= a_ev (- n t)))


(assert
 (and
  (< (* 2 (- (+ a_ev (bag.card (bag.difference_subtract UNIVERALSET f))) n))
     (+ (- n t) 1))
  (> (+ (- n t) 1) (* 2 0))))

(check-sat)
